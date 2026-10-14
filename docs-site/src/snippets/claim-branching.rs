#[k::claim(all_paths, label = "branching")]
#[k::exists(n: Int)]
#[k::ensures(k::or_bool![int::eq(n, 5), int::eq(n, 6)])]
fn branching(
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$n"), 7),
                StmtSyntax::IfThenElse(
                    k::anonymous!(Bool, "_B"),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") -> n]),
        ..state
    }
}
