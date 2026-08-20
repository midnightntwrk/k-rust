//! Rewrite-step timeout selection and moving-average accounting.

use std::{
    cell::Cell,
    time::{Duration, Instant},
};

const DEFAULT_MOVING_AVERAGE: Duration = Duration::from_secs(3);
const PREVIOUS_WEIGHT: f64 = 0.95;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    options: StepTimeoutOptions,
    moving_average_micros: Cell<Option<u64>>,
}

impl StepTimeoutController {
    pub(crate) fn new(options: StepTimeoutOptions) -> Self {
        Self {
            options,
            moving_average_micros: Cell::new(None),
        }
    }

    pub(crate) fn begin_step(&self) -> StepTimer<'_> {
        StepTimer {
            controller: self,
            started: Instant::now(),
            mode: self.timeout_mode(),
            record_elapsed: true,
        }
    }

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
    controller: &'a StepTimeoutController,
    started: Instant,
    mode: Option<StepTimeoutMode>,
    record_elapsed: bool,
}

impl StepTimer<'_> {
    pub(crate) fn timed_out(&self) -> Option<StepTimeoutMode> {
        self.mode
            .filter(|mode| self.started.elapsed() >= mode.timeout())
    }

    pub(crate) fn discard_measurement(&mut self) {
        self.record_elapsed = false;
    }
}

impl Drop for StepTimer<'_> {
    fn drop(&mut self) {
        if self.record_elapsed {
            self.controller.record(self.started.elapsed());
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
        assert!(timer.timed_out().is_some());
        timer.discard_measurement();
        drop(timer);
        assert_eq!(controller.moving_average_micros.get(), None);
    }
}
