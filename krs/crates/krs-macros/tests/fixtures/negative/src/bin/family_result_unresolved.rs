use renamed_krs::KResult;

renamed_krs::sorts! {
    Expr;
    Value: Expr + KResult;
}

// A readable family's `result` is written once and inherited by each strict
// variant, so a path that names nothing is one error, at the path.
#[renamed_krs::constructors(
    sort = Expr,
    result = KResultt //~ ERROR cannot find type `KResultt`
)]
enum Unary {
    #[renamed_krs::syntax("neg {value}")]
    #[renamed_krs::strict]
    Neg { value: Value },
    #[renamed_krs::syntax("not {value}")]
    #[renamed_krs::strict]
    Not { value: Value },
}

fn main() {}
