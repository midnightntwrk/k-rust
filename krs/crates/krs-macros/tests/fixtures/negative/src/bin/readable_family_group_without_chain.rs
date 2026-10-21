use renamed_krs::KResult;

renamed_krs::sorts! {
    Expr;
}

#[renamed_krs::constructors(sort = Expr, result = KResult)]
enum Unchained {
    #[renamed_krs::syntax("unit", group = "atoms")]
    //~^ ERROR variant group `atoms` needs a chain: `Unchained` has no `#[k::precedence]`
    Unit,
}

fn main() {}
