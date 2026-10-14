use renamed_krs::KResult;
use renamed_krs::builtin::Id;

renamed_krs::sorts! {
    Exp;
    LVal: Exp;
    impl LVal for Id;
}

#[renamed_krs::constructors(sort = Exp, result = KResult)]
#[renamed_krs::precedence((Dot))]
pub enum ExpSyntax {
    #[renamed_krs::syntax("{base}.{field}")]
    Dot { base: Exp, field: Id },
}

#[renamed_krs::constructors(sort = LVal, result = KResult)]
#[renamed_krs::precedence((LvalDot))]
pub enum LValSyntax {
    #[renamed_krs::syntax("{base}.{field}", overload = ExpSyntax::Missing)] //~ ERROR no variant named `Missing` found for enum `ExpSyntax`
    LvalDot { base: LVal, field: Id },
}

fn main() {}
