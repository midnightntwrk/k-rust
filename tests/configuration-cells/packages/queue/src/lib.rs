//! A List cell collection (KF-023): a FIFO queue of jobs.
//!
//! `<job>` is a `cell_type = "List"` collection; brackets are positional,
//! as in a Rust slice pattern: items before `..` sit at the front, items
//! after it at the back. `enqueue v` adds a job at the back and `dequeue`
//! (or `drop`, which discards it) removes the front one, so jobs leave in
//! the order they came; `front` reads the front job and `pop` removes the
//! back one.
//!
//! K closes a parent cell by adding the other instances on the right, so a
//! back instance follows a variable naming the others: `enqueue` emits
//! `<queue> _Instances0:Bag (.Bag => <job> .. </job>) </queue>`.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Enqueue, Dequeue, Drop, Front, Pop)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("enqueue {value}")] Enqueue { value: Int },
    #[k::syntax("dequeue")] Dequeue(),
    #[k::syntax("drop")] Drop(),
    #[k::syntax("front")] Front(),
    #[k::syntax("pop")] Pop(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

/// The job queue.
#[k::cell]
pub struct Queue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

/// One job.
#[k::cell]
pub struct Job {
    #[k::cell]
    pub payload: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub queue: Queue,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            queue: Queue {
                job: Job { payload: 0 },
            },
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    /// Add a job at the back.
    enqueue: {
        k: [Enqueue(v), ..],
        job: [..],
    } => {
        k: [..],
        job: [.., Job { payload: v, .. }],
    };

    /// Remove the front job and write its payload to the computation cell.
    dequeue: {
        k: [Dequeue(), ..],
        job: [first @ Job { payload: p, .. }, ..],
    } => {
        k: [p, ..],
        job: [..],
    };

    /// Remove the front job.
    drop: {
        k: [Drop(), ..],
        job: [Job { .. }, ..],
    } => {
        k: [..],
        job: [..],
    };

    /// Read the front job without removing it.
    front: {
        k: [Front(), ..],
        job: [Job { payload: p, .. }, ..],
    } => {
        k: [p, ..],
    };

    /// Remove the back job and write its payload to the computation cell.
    pop: {
        k: [Pop(), ..],
        job: [.., last @ Job { payload: p, .. }],
    } => {
        k: [p, ..],
        job: [..],
    };
}
