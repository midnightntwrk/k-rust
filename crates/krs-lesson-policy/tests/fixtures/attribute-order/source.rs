#[derive(Clone, Debug)]
#[k::constructors(sort = Expr)]
pub enum Op {
    Neg { value: Expr },
}

/// Configuration.
#[derive(Default)]
#[allow(dead_code)]
#[k::configuration]
pub struct Config {
    #[k::cell]
    k: u8,
}
