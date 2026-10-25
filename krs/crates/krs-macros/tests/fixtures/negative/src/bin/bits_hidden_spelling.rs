use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

#[k::equation]
fn code_hidden(k::term![Code(k::bits!("1_"))]: k::Term<Int>) -> k::Term<Int> {
    __krs_bits_0 //~ ERROR reserved for generated identifiers
}

fn main() {}
