//! A dependency semantics package which knows KRS only through a renamed facade.

use language_host as k;

#[k::sort(alias = BaseItem)]
pub trait BaseItemSort {}
pub type BaseItem = k::Term<dyn BaseItemSort>;

#[k::symbol("tour::BaseCommon")]
#[k::sort(alias = Common, parents = [BaseItem])]
pub trait CommonSort: BaseItemSort {}
pub type Common = k::Term<dyn CommonSort>;

#[k::symbol("tour::BaseSame")]
#[k::constructor(sort = Common, syntax = "same-base")]
pub struct Same;

#[k::constructor(sort = Common, syntax = "base-unit")]
pub struct Unit;
