//! Wall-clock phase timings for the frontend pipeline.
//!
//! A [`PhaseTimings`] is an ordered list of named durations, one per pipeline stage in call order.
//! It is a list rather than a map because some stage names legitimately repeat (sort projections
//! are generated twice, sentences are numbered twice) and the order is the information: the list
//! doubles as the documented stage order of the pipeline that produced it.
//!
//! Recording costs one [`Instant`] pair per phase, so every entry point records unconditionally
//! and the host decides whether to keep the result.

use serde::Serialize;
use web_time::Instant;

/// One named phase and its wall-clock duration in seconds.
#[derive(Clone, Debug, Serialize)]
pub struct PhaseTiming {
    pub name: &'static str,
    pub seconds: f64,
    /// Nesting depth. Top-level phases have depth zero; children recorded by
    /// [`PhaseTimings::time_nested`] have their parent's depth plus one.
    pub depth: u8,
}

/// Named phase durations in execution order.
#[derive(Clone, Debug, Default, Serialize)]
pub struct PhaseTimings {
    pub phases: Vec<PhaseTiming>,
}

impl PhaseTimings {
    /// Run `run`, then append its wall-clock duration under `name`.
    ///
    /// The value is returned unchanged, so fallible stages can be wrapped and then `?`-propagated.
    pub fn time<T>(&mut self, name: &'static str, run: impl FnOnce() -> T) -> T {
        let started = Instant::now();
        let value = run();
        self.phases.push(PhaseTiming {
            name,
            seconds: started.elapsed().as_secs_f64(),
            depth: 0,
        });
        value
    }

    /// Run a phase that records a fixed set of child phases.
    pub fn time_nested<T>(
        &mut self,
        name: &'static str,
        run: impl FnOnce(&mut PhaseTimings) -> T,
    ) -> T {
        let started = Instant::now();
        let mut children = PhaseTimings::default();
        let value = run(&mut children);
        let parent_depth = self
            .phases
            .last()
            .map_or(0, |phase| phase.depth.saturating_add(1));
        self.phases.push(PhaseTiming {
            name,
            seconds: started.elapsed().as_secs_f64(),
            depth: parent_depth.saturating_sub(1),
        });
        for phase in &mut children.phases {
            phase.depth = phase.depth.saturating_add(parent_depth);
        }
        self.phases.extend(children.phases);
        value
    }

    /// Append every phase of `other` after the phases already recorded.
    pub fn extend(&mut self, other: PhaseTimings) {
        self.phases.extend(other.phases);
    }

    /// The sum of every recorded phase; `0.0` (not `-0.0`) when nothing was recorded.
    pub fn total_seconds(&self) -> f64 {
        self.phases
            .iter()
            .filter(|phase| phase.depth == 0)
            .fold(0.0, |total, phase| total + phase.seconds)
    }

    /// The sum of every phase whose name starts with `prefix`.
    pub fn seconds_of(&self, prefix: &str) -> f64 {
        self.phases
            .iter()
            .filter(|phase| phase.depth == 0)
            .filter(|phase| phase.name.starts_with(prefix))
            .fold(0.0, |total, phase| total + phase.seconds)
    }

    /// Return the descendants immediately recorded after `name`.
    pub fn children_of(&self, name: &str) -> impl Iterator<Item = &PhaseTiming> {
        let (start, depth) = self
            .phases
            .iter()
            .enumerate()
            .find(|(_, phase)| phase.name == name)
            .map_or((self.phases.len(), 0), |(index, phase)| {
                (index + 1, phase.depth)
            });
        self.phases
            .iter()
            .enumerate()
            .skip(start)
            .take_while(move |(_, phase)| phase.depth > depth)
            .map(|(_, phase)| phase)
    }
}
