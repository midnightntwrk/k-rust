use renamed_krs as k;

#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

#[k::constructors(sort = Expr)] //~ ERROR declares it in `k::sorts!` (`Name: Outer;`) and names it with `sort = Name`
pub enum Bare {
    #[k::syntax("bare")]
    Unit,
}

fn main() {}
