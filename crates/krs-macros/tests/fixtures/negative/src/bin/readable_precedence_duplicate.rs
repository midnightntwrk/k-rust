use renamed_krs::KResult;

renamed_krs::sorts! {
    Expr;
}

#[renamed_krs::constructors(sort = Expr, result = KResult)]
#[renamed_krs::precedence((Unit, Unit))] //~ ERROR enum variant `Unit` appears more than once
enum DuplicateVariant {
    #[renamed_krs::syntax("unit")]
    Unit,
}

fn main() {}
