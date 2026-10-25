//! Two `cells!` rules on one queue, without a nondet group: `last_job` takes
//! the only job of a one-job queue and `next_job` the first job of any
//! non-empty queue. `_List_` has unit `.List`, so the queue `ListItem(J)`
//! matches both, `next_job` with an empty rest. A list item's argument has
//! no production-field sort, so each job is a named binder given a sort by
//! `where`; both rules give it the same sort, so the sorts do not separate
//! them.

use k::builtin::{Int, KSequence, List, list};

k::sorts! {
    Pgm: k::KItem;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Schedule, Idle))]
#[rustfmt::skip]
pub enum Job {
    #[k::syntax("schedule")] Schedule(),
    #[k::syntax("idle")] Idle(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub queue: List,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Pgm,
        #[k::config_var(name = "QUEUE")] queue: List,
    ) -> Self {
        Self {
            k: k::k![pgm],
            queue,
        }
    }
}

k::rules! {
    for Machine;
    use Job::*;

    last_job: {
        k: [Schedule(), ..],
        queue: list::item(job),
    } => {
        k: [Idle(), ..],
        queue: list::empty(),
    }
    where job: Int;

    next_job: {
        k: [Schedule(), ..],
        queue: list::concat(list::item(job), rest),
    } => {
        k: [..],
        queue: rest,
    }
    where job: Int;
}
