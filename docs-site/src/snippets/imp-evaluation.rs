k::rules! {
    for Expr;
    use Op::*;

    eval_neg    : Neg { value }          => -value     where value: Int;
    eval_not    : Not { value }          => !value     where value: Bool;

    eval_add    : Add { lhs, rhs }       => lhs + rhs  where lhs: Int, rhs: Int;
    eval_sub    : Sub { lhs, rhs }       => lhs - rhs  where lhs: Int, rhs: Int;
    eval_mul    : Mul { lhs, rhs }       => lhs * rhs  where lhs: Int, rhs: Int;
    eval_div    : Div { lhs, rhs }       => lhs / rhs  where lhs: Int, rhs: Int;

    eval_ge     : Ge { lhs, rhs }        => lhs >= rhs where lhs: Int, rhs: Int;
    eval_gt     : Gt { lhs, rhs }        => lhs > rhs  where lhs: Int, rhs: Int;
    eval_le     : Le { lhs, rhs }        => lhs <= rhs where lhs: Int, rhs: Int;
    eval_lt     : Lt { lhs, rhs }        => lhs < rhs  where lhs: Int, rhs: Int;

    eval_bool_eq: Eq { lhs, rhs }        => lhs == rhs where lhs: Bool, rhs: Bool;
    eval_int_eq : Eq { lhs, rhs }        => lhs == rhs where lhs: Int, rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }        => lhs != rhs where lhs: Bool, rhs: Bool;
    eval_int_ne : Ne { lhs, rhs }        => lhs != rhs where lhs: Int, rhs: Int;

    and_true    : And { lhs: true, rhs } => rhs;
    and_false   : And { lhs: false, .. } => false;
    or_true     : Or { lhs: true, .. }   => true;
    or_false    : Or { lhs: false, rhs } => rhs;
}
