use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

#[k::function(total, internal)]
pub fn Pair(first: k::Term<Int>, second: k::Term<Int>) -> k::Term<Int>;

#[k::equation]
fn pair_listed(x: Int, k::term![Pair(x, k::bits!("1_"))]: k::Term<Int>) -> k::Term<Int> { //~ ERROR write `op @ k::bits!(..)` and list `op`
    x
}

fn main() {}
