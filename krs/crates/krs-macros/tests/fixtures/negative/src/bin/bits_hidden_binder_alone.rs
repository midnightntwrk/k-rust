use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

// The hidden binder's spelling is reserved with no template in sight.
k::equations! {
    for Code;
    code_hidden: __krs_bits_0 => 1; //~ ERROR reserved for generated identifiers
}

fn main() {}
