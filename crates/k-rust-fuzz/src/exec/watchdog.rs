//! The per-case wall-clock safety limit (ARCHITECTURE 5.1): one thread per executor that cancels
//! a case's token when the case passes its deadline, and forwards the caller's cancellation to it.
//!
//! `CancellationToken::scope` installs one token and does not nest, so a case under the safety
//! limit runs in a token of its own; this thread cancels it at the deadline, or as soon as it sees
//! the caller's token cancelled. Not on wasm32, which has no threads.

use std::{
    sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError},
    thread::JoinHandle,
    time::{Duration, Instant},
};

use k_rust::backend::CancellationToken;

/// How often the watchdog looks at the caller's token while a case runs.
const CALLER_POLL: Duration = Duration::from_millis(10);

pub(super) struct Watchdog {
    shared: Arc<Shared>,
    thread: Option<JoinHandle<()>>,
}

#[derive(Default)]
struct Shared {
    state: Mutex<State>,
    wake: Condvar,
}

#[derive(Default)]
struct State {
    armed: Option<Armed>,
    shutdown: bool,
}

struct Armed {
    token: CancellationToken,
    deadline: Instant,
    caller: Option<CancellationToken>,
    /// The case's token was cancelled (by the deadline or the caller); nothing is left to do.
    done: bool,
    /// The deadline cancelled the token.
    fired: bool,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

impl Watchdog {
    pub(super) fn new() -> Self {
        let shared = Arc::new(Shared::default());
        let thread = std::thread::Builder::new()
            .name("k-rust-fuzz-watchdog".to_owned())
            .spawn({
                let shared = Arc::clone(&shared);
                move || watch(&shared)
            })
            .expect("the watchdog thread starts");
        Self {
            shared,
            thread: Some(thread),
        }
    }

    /// Arm the watchdog for one case: cancel `token` after `limit`, or when `caller` is
    /// cancelled. The returned guard disarms it.
    pub(super) fn arm(
        &self,
        token: CancellationToken,
        limit: Duration,
        caller: Option<CancellationToken>,
    ) -> ArmedGuard<'_> {
        let mut state = self.shared.lock();
        state.armed = Some(Armed {
            token,
            deadline: Instant::now() + limit,
            caller,
            done: false,
            fired: false,
        });
        drop(state);
        self.shared.wake.notify_all();
        ArmedGuard {
            shared: &self.shared,
            disarmed: false,
        }
    }
}

impl Drop for Watchdog {
    fn drop(&mut self) {
        self.shared.lock().shutdown = true;
        self.shared.wake.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

/// An armed watchdog; disarmed when dropped.
pub(super) struct ArmedGuard<'a> {
    shared: &'a Shared,
    disarmed: bool,
}

impl ArmedGuard<'_> {
    /// Disarm the watchdog; whether the deadline cancelled the case's token.
    pub(super) fn disarm(mut self) -> bool {
        self.take()
    }

    fn take(&mut self) -> bool {
        self.disarmed = true;
        let armed = self.shared.lock().armed.take();
        self.shared.wake.notify_all();
        armed.is_some_and(|armed| armed.fired)
    }
}

impl Drop for ArmedGuard<'_> {
    fn drop(&mut self) {
        if !self.disarmed {
            self.take();
        }
    }
}

fn watch(shared: &Shared) {
    let mut state = shared.lock();
    loop {
        if state.shutdown {
            return;
        }
        let wait = match state.armed.as_mut() {
            Some(armed) if !armed.done => {
                let now = Instant::now();
                if armed
                    .caller
                    .as_ref()
                    .is_some_and(CancellationToken::is_cancelled)
                {
                    armed.token.cancel();
                    armed.done = true;
                    None
                } else if now >= armed.deadline {
                    armed.token.cancel();
                    armed.done = true;
                    armed.fired = true;
                    None
                } else {
                    let remaining = armed.deadline - now;
                    Some(if armed.caller.is_some() {
                        remaining.min(CALLER_POLL)
                    } else {
                        remaining
                    })
                }
            }
            Some(_) | None => None,
        };
        state = match wait {
            Some(timeout) => {
                shared
                    .wake
                    .wait_timeout(state, timeout)
                    .unwrap_or_else(PoisonError::into_inner)
                    .0
            }
            None => shared
                .wake
                .wait(state)
                .unwrap_or_else(PoisonError::into_inner),
        };
    }
}
