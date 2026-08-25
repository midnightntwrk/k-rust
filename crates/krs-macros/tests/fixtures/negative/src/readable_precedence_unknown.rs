use renamed_krs::KResult;

renamed_krs::sorts! {
    Expr;
}

#[renamed_krs::constructors(sort = Expr, result = KResult)]
#[renamed_krs::precedence((Unti))]
enum UnknownVariant {
    #[renamed_krs::syntax("unit")]
    Unit,
}

fn main() {}
