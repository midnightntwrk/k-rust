#[k::symbol("tour::RootCommon")]
#[k::sort(alias = Common, parents = [KItem])]
pub trait CommonSort: KItemSort {}
pub type Common = Term<dyn CommonSort>;

#[k::symbol("tour::RootSame")]
#[k::constructor(sort = Common, syntax = "same-root")]
pub struct Same;

#[cfg(tour_mode = "extended")]
#[k::constructor(sort = Common, syntax = "extended-root")]
pub struct Extended;
