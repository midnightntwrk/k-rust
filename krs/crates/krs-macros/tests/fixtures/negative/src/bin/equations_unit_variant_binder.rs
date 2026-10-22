use renamed_krs as k;
use renamed_krs::builtin::Int;

renamed_krs::sorts! {
    Reg8;
}

#[k::constructors(sort = Reg8, result = renamed_krs::KResult)]
#[k::precedence((Ra, Rb))]
pub enum Register {
    #[k::syntax("ra")]
    Ra,
    #[k::syntax("rb")]
    Rb,
}

#[k::function(total, internal)]
pub fn Index(register: k::Term<Reg8>) -> k::Term<Int>;

// A bare `Ra` is a binder in a pattern; rustc rejects it where `Ra` names a
// unit variant, which `Ra()` or `Register::Ra` spells. (A name spelled as a
// constant, such as `RA`, is no binder: it names what it resolves to.)
k::equations! {
    for Index;
    use Register::*;
    index_a: Ra => 0; //~ ERROR mismatched types
    index_b: Register::Rb => 1;
}

fn main() {}
