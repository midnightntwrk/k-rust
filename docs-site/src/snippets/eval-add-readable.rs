k::rules! {
    for Expr;
    use Op::*;

    eval_add    : Add { lhs, rhs }       => lhs + rhs  where lhs: Int, rhs: Int;
}
