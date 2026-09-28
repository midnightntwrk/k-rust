use renamed_krs as k;

#[k::sort]
pub trait Expr {}

#[k::constructors(sort = Expr)]
pub enum Bad {
    Tuple(k::Term<dyn Expr>), //~ ERROR tuple enum constructor variants are unsupported
}

fn main() {}
