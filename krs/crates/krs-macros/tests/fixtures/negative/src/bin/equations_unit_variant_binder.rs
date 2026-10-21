use renamed_krs as k;
use renamed_krs::builtin::Int;

renamed_krs::sorts! {
    Reg8;
}

#[k::constructors(sort = Reg8, result = renamed_krs::KResult)]
#[k::precedence((A, B))]
pub enum Register {
    #[k::syntax("ra")]
    A,
    #[k::syntax("rb")]
    B,
}

#[k::function(total, internal)]
pub fn Index(register: k::Term<Reg8>) -> k::Term<Int>;

// A bare `A` is a binder in a pattern; rustc rejects it where `A` names a
// unit variant, which `A()` or `Register::A` spells.
k::equations! {
    for Index;
    use Register::*;
    index_a: A => 0; //~ ERROR mismatched types
    index_b: Register::B => 1;
}

fn main() {}
