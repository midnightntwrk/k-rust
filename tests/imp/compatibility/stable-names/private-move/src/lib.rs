pub mod api {
    #[k::sort]
    pub trait Expr {}

    #[k::constructor(sort = Expr, syntax = "publicValue")]
    pub struct PublicValue;
}

mod internal_new {
    use crate::api::Expr;

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
            k: k::configuration::KCell::new(k::k![api::PublicValue]),
        }
    }
}
