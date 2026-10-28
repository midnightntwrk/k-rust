use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::constructor(sort = Int, syntax = "seven")]
pub struct Seven;

k::equations! {
    for Seven; //~ ERROR [krs::syntax::invalid-equation-table] `Seven` is not a non-parametric `#[k::function]`
    zero: () => 1;
}

fn main() {}
