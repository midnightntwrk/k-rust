k::rules! {
    for Expr;
    use Op::*;

    eval_neg    : Neg { value }          => int::sub(0, value);
    eval_not    : Not { value }          => bool::not(value);

    eval_add    : Add { lhs, rhs }       => int::add(lhs, rhs);
    eval_sub    : Sub { lhs, rhs }       => int::sub(lhs, rhs);
    eval_mul    : Mul { lhs, rhs }       => int::mul(lhs, rhs);
    eval_div    : Div { lhs, rhs }       => int::div(lhs, rhs);

    eval_ge     : Ge { lhs, rhs }        => int::ge(lhs, rhs);
    eval_gt     : Gt { lhs, rhs }        => int::gt(lhs, rhs);
    eval_le     : Le { lhs, rhs }        => int::le(lhs, rhs);
    eval_lt     : Lt { lhs, rhs }        => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }        => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_eq : Eq { lhs, rhs }        => int::eq(lhs, rhs)  where lhs: Int, rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }        => bool::ne(lhs, rhs) where lhs: Bool, rhs: Bool;
    eval_int_ne : Ne { lhs, rhs }        => int::ne(lhs, rhs)  where lhs: Int, rhs: Int;

    and_true    : And { lhs: true, rhs } => rhs;
    and_false   : And { lhs: false, .. } => false;
    or_true     : Or { lhs: true, .. }   => true;
    or_false    : Or { lhs: false, rhs } => rhs;
}
