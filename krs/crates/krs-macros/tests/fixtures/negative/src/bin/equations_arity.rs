use renamed_krs as k;
use renamed_krs::builtin::{Bool, Int};

#[k::function(total, internal)]
pub fn Pick(flag: k::Term<Bool>, value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Pick;
    pick_true: (true, v) => v;
    pick_short: false => 0; //~ ERROR mismatched types
}

fn main() {}
