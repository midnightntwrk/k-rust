use renamed_krs as k;

k::sorts! {
    Expr;
}

mod first {
    use super::Expr;
    use renamed_krs as k;

    #[k::constructors(sort = Expr, result = k::KResult)]
    #[k::precedence((Shared))]
    pub enum Family {
        #[k::syntax("first({value})")]
        Shared { value: Expr },
    }
}

mod second {
    use super::Expr;
    use renamed_krs as k;

    #[k::constructors(sort = Expr, result = k::KResult)]
    #[k::precedence((Shared))]
    pub enum Family {
        #[k::syntax("second({value})")]
        Shared { value: Expr },
    }
}

use first::Family::*;
use second::Family::*;

k::rules! {
    for Expr;
    ambiguous: Shared { value } => value; //~ ERROR `Shared` is ambiguous
}

fn main() {}
