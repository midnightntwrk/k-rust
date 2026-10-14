//! `program` asserts program syntax, so an automatic placement is a warning.
//!
//! `LogRecord::Entry` has a `List` field, and K 7.1.337 has no LIST-SYNTAX
//! module: KRS places it in `KRS-PROGRAM-WARNING` and warns.

use k::builtin::{Bytes, Int, KSequence, List};

k::sorts! {
    LogEntry;
}

#[k::constructors(sort = LogEntry, result = k::KResult)]
#[k::precedence((Entry))]
pub enum LogRecord {
    #[k::syntax("logEntry({address}, {topics}, {data})", program)]
    Entry {
        address: Int,
        topics: List,
        data: Bytes,
    },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}
