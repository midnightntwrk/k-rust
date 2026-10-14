#[k::claim(all_paths, label = "sum-spec", circularity)]
#[k::requires(int::ge(n, 0))]
fn sum_spec(
    n: Term<Int>,
    s: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::While(
                Op::Not(Op::Le(k::id!("$n"), 0)),
                StmtSyntax::Block(StmtSyntax::Sequence(
                    StmtSyntax::Assign(k::id!("$s"), Op::Add(k::id!("$s"), k::id!("$n"))),
                    StmtSyntax::Assign(k::id!("$n"), Op::Add(k::id!("$n"), Op::Neg(1))),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") -> n,
            k::id!("$s") -> s,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") -> 0,
            k::id!("$s") -> int::add(
                s,
                int::div(int::mul(int::add(n, 1), n), 2),
            ),
        ]),
        ..state
    }
}
