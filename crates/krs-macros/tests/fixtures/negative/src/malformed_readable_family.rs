use renamed_krs::KResult;

renamed_krs::sorts! {
    Expr;
}

#[renamed_krs::constructors(sort = Expr, result = KResult)]
#[renamed_krs::precedence((Unit))]
enum MissingVariant {
    #[renamed_krs::syntax("unit")]
    Unit,
    #[renamed_krs::syntax("other")]
    Other,
}

fn main() {}
