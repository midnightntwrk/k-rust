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
    /// The steps whose time the moving average took in.
    #[cfg(all(test, not(target_arch = "wasm32")))]
    pub(crate) recorded: Cell<usize>,
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
            #[cfg(all(test, not(target_arch = "wasm32")))]
            recorded: Cell::new(0),
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
                off_the_clock: crate::stop::time_off_the_clock(),
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
        #[cfg(test)]
        self.recorded.set(self.recorded.get() + 1);
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
    /// The thread's time off the clock when the step began (`stop::off_the_clock`): the step's
    /// measured time leaves out what it spent there since.
    #[cfg(not(target_arch = "wasm32"))]
    off_the_clock: Duration,
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
                let off = crate::stop::time_off_the_clock().saturating_sub(self.off_the_clock);
                self.controller
                    .record(self.started.elapsed().saturating_sub(off));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn with_both_timeouts_the_moving_average_applies_while_below_the_manual_one() {
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
        assert_eq!(
            crate::stop::check().map_err(crate::stop::Stop::into_cause),
            Ok(())
        );
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        {
            let _timer = controller.begin_step();
            assert!(
                crate::stop::check()
                    .map_err(crate::stop::Stop::into_cause)
                    .is_err()
            );
        }
        assert_eq!(
            crate::stop::check().map_err(crate::stop::Stop::into_cause),
            Ok(())
        );
    }

    /// Work off the clock (`stop::off_the_clock`, a condition record's evaluation) is not
    /// charged to the step: the deadline is lifted while it runs, moved later by its time
    /// afterwards, and its time is left out of the step's measurement.
    #[test]
    fn work_off_the_clock_is_not_charged_to_the_step() {
        let check = || crate::stop::check().map_err(crate::stop::Stop::into_cause);
        // A deadline already passed does not stop work off the clock, and still stops the step.
        let passed = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        {
            let _timer = passed.begin_step();
            let (inside, spent) = crate::stop::off_the_clock(u64::MAX, check);
            assert_eq!(inside, Ok(()));
            assert!(!spent);
            assert!(check().is_err());
        }
        // A deadline 300 ms away is still 300 ms away after 600 ms off the clock.
        let later = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::from_millis(300)),
            moving_average: false,
        });
        {
            let _timer = later.begin_step();
            let ((), _) = crate::stop::off_the_clock(u64::MAX, || {
                std::thread::sleep(Duration::from_millis(600));
            });
            assert_eq!(check(), Ok(()));
        }
        assert_eq!(
            later
                .moving_average_micros
                .get()
                .map(|micros| micros < 300_000),
            Some(true)
        );
        // The work's own budget bounds it instead.
        let (inside, spent) = crate::stop::off_the_clock(0, check);
        assert!(inside.is_err());
        assert!(spent);
        assert_eq!(check(), Ok(()));
    }

    #[test]
    fn nested_steps_preserve_the_earliest_deadline() {
        let outer = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let inner = StepTimeoutController::new(StepTimeoutOptions::default());

        let _outer_timer = outer.begin_step();
        assert!(
            crate::stop::check()
                .map_err(crate::stop::Stop::into_cause)
                .is_err()
        );
        {
            let _inner_timer = inner.begin_step();
            assert!(
                crate::stop::check()
                    .map_err(crate::stop::Stop::into_cause)
                    .is_err()
            );
        }
        assert!(
            crate::stop::check()
                .map_err(crate::stop::Stop::into_cause)
                .is_err()
        );
    }
}
