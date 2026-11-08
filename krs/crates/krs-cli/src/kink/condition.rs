//! `[stop] when` in a KRS corpus: a stop condition named with KRS's spellings, as `krs run
//! --stop-when` and a case's `run.stop_when` name one (krs-exec [`krs_exec::condition`]): the
//! function by its KRS path, the cells by Rust field path, and the observer it is evaluated in as
//! `PACKAGE:DEFINITION`, by default the corpus's own definition, the baseline.
//!
//! The front end resolves the condition before anything runs, through krs-exec's own resolver
//! ([`krs_exec::Semantics::stop_condition`]), so a condition is refused here exactly where `krs
//! run` refuses it, with its message (stage `stop`, reason `stop-condition-unresolved`), and hands
//! kink-campaign the condition ([`kink_flow::StopWhen`]): an identity, which every key and
//! document of a run with the stop names, and an oracle, which asks the condition at each arrival
//! of a run. The oracle reads each run's cells with the baseline's declarations and evaluates the
//! function in the observer, never in the definition being run, so the baseline and every mutant
//! are asked one question; kink-campaign does not admit a mutant that declares a sort or symbol
//! the read cells reach otherwise than the baseline (`stop-condition-incompatible`), and the
//! oracle refuses a cell holding a symbol the baseline does not declare.
//!
//! The observer is loaded once per thread that runs a program, as a view's observer is
//! ([`super::render::Observers`]); the baseline as observer is a load of its own, apart from the
//! compile that reads the corpus's typed inputs. Each evaluation is bounded by the view budget
//! `krs run` gives one by default ([`crate::DEFAULT_VIEW_BUDGET`]).
//!
//! The identity is `{observer: {definition, definition_ir}, function, cells}`: the observer's
//! name as written (`null` for the baseline) and its Definition IR digest (the digest the
//! evidence's identity names, [`super::render::definition_digest`]), the function's full KRS path
//! and the cells as written. The digest decides every answer the observer gives, and the path and
//! the cells which question it is asked.

use std::sync::Arc;

use k_rust::backend::StopCondition;
use kink_flow::{StopOracle, StopWhen};
use krs_exec::{ArrivalObservation, ConditionOracle, ResolvedCondition, Semantics};
use serde_json::{Value, json};

use super::inputs::KrsInputs;
use super::render::{Observer, Observers, definition_digest};

/// Why a corpus's `[stop] when` cannot be bound: the reason and detail of its refusal at stage
/// `stop`.
pub(crate) struct Unbound {
    pub(crate) reason: &'static str,
    pub(crate) detail: String,
}

/// Where the cells a condition reads are decoded: the observer's own load when the observer is
/// the baseline (the same Definition IR), else the compile that reads the corpus's inputs.
pub(crate) enum Subject {
    Observer,
    Inputs(Arc<KrsInputs>),
}

/// The oracle of one corpus's stop condition ([`StopOracle`]).
pub(crate) struct KrsCondition {
    when: krs_exec::StopWhen,
    observer: Arc<Observer>,
    subject: Subject,
    cells: Vec<Vec<String>>,
}

impl KrsCondition {
    /// The condition `when` of the corpus whose definition is `definition`, resolved: its
    /// observer prepared (`observers` holds a named one; the baseline is `definition` itself),
    /// the function and the cells resolved as `krs run` resolves them, and its identity.
    ///
    /// # Errors
    ///
    /// `stop-condition-unresolved` with krs-exec's refusal of the condition or of its observer.
    pub(crate) fn bind(
        when: krs_exec::StopWhen,
        definition: &krs_ir_levels::DefinitionIr,
        inputs: &Arc<KrsInputs>,
        observers: &Observers,
    ) -> Result<StopWhen, Unbound> {
        let function = when.function.clone();
        let unresolved = |detail: String| Unbound {
            reason: "stop-condition-unresolved",
            detail: format!("[stop] when `{function}`: {detail}"),
        };
        let named = match &when.observer {
            Some(name) => observers
                .get(name)
                .map_err(|reason| unresolved(format!("the observer `{name}`: {reason}")))?,
            None => None,
        };
        let (observer, subject) = match named {
            Some(observer) => (observer, Subject::Inputs(Arc::clone(inputs))),
            None => (
                Arc::new(
                    Observer::compile("the definition", definition.clone()).map_err(unresolved)?,
                ),
                Subject::Observer,
            ),
        };
        let mut condition = Self {
            when,
            observer,
            subject,
            cells: Vec::new(),
        };
        let resolved = condition
            .observer
            .with_loaded(|observer| condition.resolve(observer))
            .map_err(unresolved)?;
        condition.cells = resolved.cell_symbols().map(<[String]>::to_vec).collect();
        let digest = definition_digest(condition.observer.definition()).map_err(unresolved)?;
        let identity = json!({
            "observer": {
                "definition": condition.when.observer,
                "definition_ir": digest,
            },
            "function": resolved.function_path(),
            "cells": condition.when.cells,
        });
        Ok(StopWhen::new(identity, Arc::new(condition)))
    }

    /// The condition resolved for runs of the baseline, evaluated in `observer` (this
    /// condition's observer, loaded on this thread).
    fn resolve(&self, observer: &Semantics) -> Result<ResolvedCondition, String> {
        match &self.subject {
            Subject::Observer => observer
                .stop_condition(observer, &self.when)
                .map_err(|error| error.to_string()),
            Subject::Inputs(inputs) => {
                inputs.with_semantics("reading a stop condition's cells", |subject| {
                    subject
                        .stop_condition(observer, &self.when)
                        .map_err(|error| error.to_string())
                })
            }
        }
    }
}

impl StopOracle for KrsCondition {
    fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    fn with_condition(&self, body: &mut dyn FnMut(&mut dyn StopCondition)) -> Result<(), String> {
        self.observer.with_loaded(|observer| {
            let resolved = self.resolve(observer)?;
            let observation =
                ArrivalObservation::new(&resolved, observer, Some(crate::DEFAULT_VIEW_BUDGET))
                    .map_err(|error| error.to_string())?;
            let mut oracle = ConditionOracle::new(observation);
            body(&mut oracle);
            Ok(())
        })
    }
}

/// The condition as the corpus wrote it, which the documents' `stop.krs.when` names: the
/// function, the cells and the observer (`null` for the baseline).
pub(crate) fn written(when: &kink_flow::StopWhenSection) -> Value {
    json!({
        "function": when.function,
        "cells": when.cells,
        "observer": when.observer,
    })
}
