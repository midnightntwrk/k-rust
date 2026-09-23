#[derive(Clone)]
#[k::constructors(sort = Expr)]
pub enum Op {
    Neg { value: Expr },
}

pub static __KRS_REGISTRATIONS: u8 = 0;
