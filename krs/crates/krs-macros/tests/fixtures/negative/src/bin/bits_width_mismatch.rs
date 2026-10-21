use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_low: k::bits!("0yyy yyyy") => y;
    code_high: k::bits!("1 yyy yyy") => 0; //~ ERROR match argument 1 with bit templates 8 and 7 bits wide
}

fn main() {}
