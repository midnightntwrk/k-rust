//! KEVM's `LogRecord::Entry` and `BlockHashLookup` without placement markers.
//!
//! Both are `pub`, but K 7.1.337 has no LIST-SYNTAX module, so KRS places
//! them in `KRS-EVM` rather than `KRS-EVM-SYNTAX`: rules may use them and
//! programs cannot contain them. `krs check --partition` lists the placement.

use k::builtin::{Bytes, Int, KSequence, List};

k::sorts! {
    LogEntry;
    Command: k::KItem;
}

#[k::constructors(sort = LogEntry, result = k::KResult)]
#[k::precedence((Entry))]
pub enum LogRecord {
    #[k::syntax("logEntry({address}, {topics}, {data})")]
    Entry {
        address: Int,
        topics: List,
        data: Bytes,
    },
}

#[k::function(partial, sort = Int, syntax = "#kevmBlockHash({hashes}, {requested})")]
pub struct BlockHashLookup {
    pub hashes: k::Term<List>,
    pub requested: k::Term<Int>,
}

#[k::constructors(sort = Command, result = k::KResult)]
#[k::precedence((Emit, Done))]
pub enum Commands {
    #[k::syntax("emit({address})")]
    Emit { address: Int },
    #[k::syntax("done")]
    Done(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Command) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Command;
    use Commands::*;

    emit: Emit { address: _ } => Done();
}
