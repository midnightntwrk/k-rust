pub mod moved_api {
    #[k::sort(alias = Expr)]
    pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

    #[k::constructor(sort = Expr, syntax = "publicValue")]
    pub struct PublicValue;
}

pub use moved_api::{Expr, PublicValue};

mod internal_old {
    use crate::moved_api::Expr;

    #[allow(dead_code)]
    #[k::constructor(sort = Expr, syntax = "privateValue")]
    struct PrivateValue;
}

#[k::configuration(root = "stableNames")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![moved_api::PublicValue]),
        }
    }
}
