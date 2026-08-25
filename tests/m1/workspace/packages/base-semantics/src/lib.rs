//! A dependency semantics package which knows KRS only through a renamed facade.

use language_host as k;

#[k::sort]
pub trait BaseItem {}

#[k::sort]
pub trait Common: BaseItem {}

#[k::constructor(sort = Common, syntax = "same-base")]
pub struct Same;

#[k::constructor(sort = Common, syntax = "base-unit")]
pub struct Unit;

pub mod nested {
    use super::k;

    #[k::sort]
    pub trait Common {}

    #[k::constructor(sort = Common, syntax = "same-base-nested")]
    pub struct Same;
}

/// A reachable name used only to satisfy the current collector-entrypoint plan model.
pub fn collector_anchor() {}

