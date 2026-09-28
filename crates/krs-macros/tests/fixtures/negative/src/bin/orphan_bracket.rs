use renamed_krs as k;

#[k::bracket("({value})")] //~ ERROR is a sort helper; place `#[k::sort]` before it
#[k::sort]
pub trait Expr {}

fn main() {}
