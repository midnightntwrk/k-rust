#[k::sort]
pub trait Expr {}

#[k::configuration(root = "diagnostic")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![first::Collision]),
        }
    }
}

pub mod first {
    use crate::Expr;

    #[k::constructor(sort = Expr, syntax = "first")]
    pub struct Collision;
}

pub mod second {
    use crate::Expr;

    // Exact cross-item diagnostic anchor: this second `Collision` emits the
    // same public K symbol as `first::Collision`.
    #[k::constructor(sort = Expr, syntax = "second")]
    pub struct Collision;
}
