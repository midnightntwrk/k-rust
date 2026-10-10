use renamed_krs as k;

#[k::bracket("({value})")] //~ ERROR is a sort helper; place `#[k::sort]` before it
#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

fn main() {}
