//! A dependency semantics package which knows KRS only through a renamed facade.

use language_host as k;

#[k::sort]
pub trait BaseItem {}

#[k::symbol("tour::BaseCommon")]
#[k::sort]
pub trait Common: BaseItem {}

#[k::symbol("tour::BaseSame")]
#[k::constructor(sort = Common, syntax = "same-base")]
pub struct Same;

#[k::constructor(sort = Common, syntax = "base-unit")]
pub struct Unit;

/// A reachable name used only to satisfy the current collector-entrypoint plan model.
pub fn collector_anchor() {}
