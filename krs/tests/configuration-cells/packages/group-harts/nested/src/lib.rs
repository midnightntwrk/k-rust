//! Clusters of harts: a Map collection of harts inside each instance of a
//! Map collection of clusters.
//!
//! The library's rules for `Hart` are local steps of one hart of one
//! cluster. The rules between the harts of a cluster are the cluster's own
//! (`for Cluster`), so each is a local step of one cluster: `spawn`, `join`,
//! `read` and `write` work as in `smp`, over the cluster's harts and its own
//! memory.

use hart::{BusOp, Hart, Job, Jobs, Op, Prog, Regs};
use k::builtin::{Int, Map, int, map};

/// The clusters.
#[k::cell]
pub struct Clusters {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub cluster: Cluster,
}

/// One cluster, keyed by `cid`: its harts, its memory and the key of the
/// next hart it starts.
#[k::cell]
pub struct Cluster {
    #[k::cell]
    pub cid: Int,
    #[k::cell(nested)]
    pub harts: Harts,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell(name = "nextId")]
    pub next_id: Int,
}

/// A cluster's harts.
#[k::cell]
pub struct Harts {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub hart: Hart,
}

#[k::configuration]
pub struct Board {
    #[k::cell(nested)]
    pub clusters: Clusters,
}

impl Board {
    #[k::init]
    pub fn init(pgm: Prog) -> Self {
        Self {
            clusters: Clusters {
                cluster: Cluster {
                    cid: 0,
                    harts: Harts {
                        hart: Hart {
                            id: 0,
                            k: k::k![pgm],
                            pc: 0,
                            regs: Regs { a: 1, b: 2 },
                            reservation: k::absent!(0),
                            jobs: Jobs {
                                job: Job { jid: 0, payload: 0 },
                            },
                        },
                    },
                    mem: map::empty(),
                    next_id: 1,
                },
            },
        }
    }
}

k::rules! {
    for Cluster;
    use BusOp::*;
    use Op::*;

    /// Start a hart of this cluster keyed by `nextId`, running `body`.
    spawn: {
        hart: { me @ Hart { k: [Spawn { body }, ..], .. }, .. },
        next_id: n,
    } => {
        hart: { Hart { k: [..], ..me }, Hart { id: n, k: [body], .. }, .. },
        next_id: int::add(n, 1),
    };

    /// Wait until hart `n` of this cluster has finished, then remove it.
    join: {
        hart: { me @ Hart { k: [Join { id: n }, ..], .. }, Hart { id: n, k: [], .. }, .. },
    } => {
        hart: { Hart { k: [..], ..me }, .. },
    };

    /// Answer a read with the value at `addr` of this cluster's memory.
    read: {
        hart: { me @ Hart { k: [Read { addr }, ..], .. }, .. },
        mem: { addr -> value, .. },
    } => {
        hart: { Hart { k: [value, ..], ..me }, .. },
    };

    /// Write `value` at `addr` of this cluster's memory.
    write: {
        hart: { me @ Hart { k: [Write { addr, value }, ..], .. }, .. },
        mem,
    } => {
        hart: { Hart { k: [..], ..me }, .. },
        mem: map::update(mem, addr, value),
    };
}
