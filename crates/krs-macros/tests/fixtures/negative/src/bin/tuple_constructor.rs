use krs_macros::constructor;

trait Expr {}

#[constructor(sort = Expr)]
struct Tuple(renamed_krs::Term<dyn Expr>); //~ ERROR tuple structs are not supported

fn main() {}
