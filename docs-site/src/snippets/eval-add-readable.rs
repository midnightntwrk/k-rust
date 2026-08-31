k::rules! {
    in Machine.k;

    eval_add    : Add { lhs, rhs }       => int::add(lhs, rhs);
}
