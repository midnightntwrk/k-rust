use renamed_krs as k;

#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

#[k::constructors(sort = Expr)]
pub enum Bad {
    Tuple(k::Term<dyn ExprSort>), //~ ERROR tuple enum constructor variants are unsupported
}

fn main() {}
