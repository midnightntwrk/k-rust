use renamed_krs as k;

pub trait Expr {}
pub trait Value {}

#[k::seqstrict(sequence = [value], result = Value)] //~ ERROR is a constructor helper; place `#[k::constructor(...)]` before it
#[k::constructor(sort = Expr)]
pub struct Wrapped {
    pub value: k::Term<dyn Expr>,
}

fn main() {}
