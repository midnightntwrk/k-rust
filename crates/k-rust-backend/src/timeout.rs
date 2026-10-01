//! Rewrite-step timeout selection and moving-average accounting.

use std::time::Duration;

#[cfg(not(target_arch = "wasm32"))]
use std::{cell::Cell, time::Instant};

#[cfg(not(target_arch = "wasm32"))]
use crate::stop::{DeadlineGuard, arm_deadline};

#[cfg(not(target_arch = "wasm32"))]
const DEFAULT_MOVING_AVERAGE: Duration = Duration::from_secs(3);
#[cfg(not(target_arch = "wasm32"))]
const PREVIOUS_WEIGHT: f64 = 0.95;

/// Return whether the request was cancelled, a solver prelude failed, or the active rewrite/proof
/// step has exhausted its deadline: whether any signal of the `stop` registry is raised.
///
/// No production code calls this predicate: native hooks and the simplifier's fixed-point loops
/// poll `stop::check`. It is kept for its tests until CBC-04-T11. The deadline is armed by
/// `StepTimeoutController::begin_step` in the thread-local registry, and nested timers restore
/// the previous deadline when they leave scope.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no production caller once hooks poll `stop::check`; deleted with its shim by CBC-04-T11"
    )
)]
pub(crate) fn interruption_requested() -> bool {
    crate::stop::legacy_interruption_requested()
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StepTimeoutMode {
    Manual(Duration),
    MovingAverage(Duration),
}

impl StepTimeoutMode {
    pub fn timeout(self) -> Duration {
        match self {
            Self::Manual(timeout) => timeout,
            Self::MovingAverage(average) => average.saturating_mul(2),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StepTimeoutOptions {
    pub manual: Option<Duration>,
    pub moving_average: bool,
}

pub(crate) struct StepTimeoutController {
    #[cfg(not(target_arch = "wasm32"))]
    options: StepTimeoutOptions,
    #[cfg(not(target_arch = "wasm32"))]
    moving_average_micros: Cell<Option<u64>>,
}

impl StepTimeoutController {
    pub(crate) fn new(options: StepTimeoutOptions) -> Self {
        #[cfg(target_arch = "wasm32")]
        let _ = options;
        Self {
            #[cfg(not(target_arch = "wasm32"))]
            options,
            #[cfg(not(target_arch = "wasm32"))]
            moving_average_micros: Cell::new(None),
        }
    }

    pub(crate) fn begin_step(&self) -> StepTimer<'_> {
        #[cfg(target_arch = "wasm32")]
        {
            StepTimer {
                _controller: std::marker::PhantomData,
                record_elapsed: false,
            }
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            let started = Instant::now();
            let mode = self.timeout_mode();
            let deadline = mode.and_then(|mode| {
                let deadline = started.checked_add(mode.timeout())?;
                Some(arm_deadline(deadline, mode))
            });
            StepTimer {
                controller: self,
                started,
                _deadline: deadline,
                record_elapsed: true,
            }
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn timeout_mode(&self) -> Option<StepTimeoutMode> {
        let average = self
            .moving_average_micros
            .get()
            .map(Duration::from_micros)
            .unwrap_or(DEFAULT_MOVING_AVERAGE);
        match (self.options.manual, self.options.moving_average) {
            (None, false) => None,
            (Some(manual), false) => Some(StepTimeoutMode::Manual(manual)),
            (None, true) => Some(StepTimeoutMode::MovingAverage(average)),
            (Some(manual), true) if average < manual => {
                Some(StepTimeoutMode::MovingAverage(average))
            }
            (Some(manual), true) => Some(StepTimeoutMode::Manual(manual)),
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn record(&self, elapsed: Duration) {
        let elapsed = u64::try_from(elapsed.as_micros()).unwrap_or(u64::MAX);
        let next = self.moving_average_micros.get().map_or(elapsed, |average| {
            (PREVIOUS_WEIGHT * average as f64 + (1.0 - PREVIOUS_WEIGHT) * elapsed as f64).floor()
                as u64
        });
        self.moving_average_micros.set(Some(next));
    }
}

pub(crate) struct StepTimer<'a> {
    #[cfg(target_arch = "wasm32")]
    _controller: std::marker::PhantomData<&'a StepTimeoutController>,
    #[cfg(not(target_arch = "wasm32"))]
    controller: &'a StepTimeoutController,
    #[cfg(not(target_arch = "wasm32"))]
    started: Instant,
    /// The step's deadline, armed in the `stop` registry: a poll after it passed returns
    /// `StopCause::Deadline` with its mode. Restores the enclosing step's deadline when the
    /// timer is dropped.
    #[cfg(not(target_arch = "wasm32"))]
    _deadline: Option<DeadlineGuard>,
    record_elapsed: bool,
}

impl StepTimer<'_> {
    pub(crate) fn discard_measurement(&mut self) {
        self.record_elapsed = false;
    }
}

impl Drop for StepTimer<'_> {
    fn drop(&mut self) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            if self.record_elapsed {
                self.controller.record(self.started.elapsed());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn follows_the_reference_timeout_selection_policy() {
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::from_secs(10)),
            moving_average: true,
        });
        assert_eq!(
            controller.timeout_mode(),
            Some(StepTimeoutMode::MovingAverage(Duration::from_secs(3)))
        );
        assert_eq!(
            controller.timeout_mode().unwrap().timeout(),
            Duration::from_secs(6)
        );

        controller.moving_average_micros.set(Some(12_000_000));
        assert_eq!(
            controller.timeout_mode(),
            Some(StepTimeoutMode::Manual(Duration::from_secs(10)))
        );
    }

    #[test]
    fn weights_the_previous_average_at_ninety_five_percent() {
        let controller = StepTimeoutController::new(StepTimeoutOptions::default());
        controller.record(Duration::from_micros(1_000));
        controller.record(Duration::from_micros(2_000));
        assert_eq!(controller.moving_average_micros.get(), Some(1_050));
    }

    #[test]
    fn timed_out_steps_do_not_skew_the_average() {
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let mut timer = controller.begin_step();
        assert_eq!(
            crate::stop::check().map_err(crate::stop::Stop::into_cause),
            Err(crate::stop::StopCause::Deadline(StepTimeoutMode::Manual(
                Duration::ZERO
            )))
        );
        timer.discard_measurement();
        drop(timer);
        assert_eq!(controller.moving_average_micros.get(), None);
    }

    #[test]
    fn exposes_and_restores_the_active_step_deadline() {
        assert!(!interruption_requested());
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        {
            let _timer = controller.begin_step();
            assert!(interruption_requested());
        }
        assert!(!interruption_requested());
    }

    #[test]
    fn nested_steps_preserve_the_earliest_deadline() {
        let outer = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let inner = StepTimeoutController::new(StepTimeoutOptions::default());

        let _outer_timer = outer.begin_step();
        assert!(interruption_requested());
        {
            let _inner_timer = inner.begin_step();
            assert!(interruption_requested());
        }
        assert!(interruption_requested());
    }
}
