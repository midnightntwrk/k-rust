k::rules! {
    for Expr;
    use Op::*;

    eval_add    : Add { lhs, rhs }       => int::add(lhs, rhs);
}
