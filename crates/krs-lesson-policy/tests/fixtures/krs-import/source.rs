use k::sorts;
use k::{KResult, rules as r};
use k::*;
use k as facade;
use std::vec as k;

mod k {}

sorts! {
    M: KResult;
}

#[constructors(sort = M, result = KResult)]
pub enum E {}
