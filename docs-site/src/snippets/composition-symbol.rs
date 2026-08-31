#[k::symbol("tour::RootCommon")]
#[k::sort]
pub trait Common: KItem {}

#[k::symbol("tour::RootSame")]
#[k::constructor(sort = Common, syntax = "same-root")]
pub struct Same;

#[cfg(tour_mode = "extended")]
#[k::constructor(sort = Common, syntax = "extended-root")]
pub struct Extended;
