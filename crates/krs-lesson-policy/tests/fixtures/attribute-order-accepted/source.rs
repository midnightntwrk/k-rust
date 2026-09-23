#[k::constructors(sort = Expr)]
#[derive(Clone, Debug)]
#[rustfmt::skip]
pub enum Op {
    Neg { value: Expr },
}

#[rustfmt::skip]
/// Doc comments and inert attributes may precede the KRS attribute.
#[allow(dead_code)]
#[k::configuration]
pub struct Config {
    #[k::cell]
    k: u8,
}

#[derive(Clone)]
pub struct Plain;
