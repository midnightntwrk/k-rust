#[k::sort]
pub trait Expr {}

// The exact malformed token is `syntax`; `sort = ...` is required.
#[k::constructor(syntax = "broken")]
pub struct Broken;
