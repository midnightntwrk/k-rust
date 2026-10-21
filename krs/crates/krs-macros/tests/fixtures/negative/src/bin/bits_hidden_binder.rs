use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Pair(first: k::Term<Int>, second: k::Term<Int>) -> k::Term<Int>;

// A hand-written binder spelled like the hidden binder of the unnamed
// template beside it would alias that binder; it is reserved.
#[k::equation]
fn pair_hidden(k::term![Pair(k::bits!("1_"), __krs_bits_0)]: k::Term<Int>) -> k::Term<Int> { //~ ERROR reserved for generated identifiers
    __krs_bits_0
}

fn main() {}
