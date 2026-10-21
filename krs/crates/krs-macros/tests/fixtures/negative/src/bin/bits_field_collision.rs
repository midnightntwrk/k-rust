use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

#[k::function(total, internal)]
pub fn Pair(first: k::Term<Int>, second: k::Term<Int>) -> k::Term<Int>;

#[k::equation]
fn pair_low(k::term![Pair(k::bits!("yy"), y)]: k::Term<Int>) -> k::Term<Int> { //~ ERROR field `y` of the bit template is also a binder of the pattern
    y
}

fn main() {}
