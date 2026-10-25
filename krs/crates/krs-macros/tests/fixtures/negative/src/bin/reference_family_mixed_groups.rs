renamed_krs::sorts! {
    Expr;
}

#[renamed_krs::constructors(sort = Expr, reference)]
enum Mixed {
    #[renamed_krs::syntax("unit", group = "atoms", format = "unit")]
    Unit,
    #[renamed_krs::syntax("other", format = "other")]
    Other, //~ ERROR reference family `Mixed` gives `group` to some variants but not to `Other`
}

fn main() {}
