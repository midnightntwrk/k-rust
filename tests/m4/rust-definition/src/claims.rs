//! Complete M4 proof corpus: all 15 upstream IMP claims plus five adjuncts.

use k::Term;
use k::builtin::{Bool, Int, Map, bool, int};
#[allow(unused_imports)]
use k::map;

use crate::static_adjunct::{M3dPositive, M3dPriority, M3dTotal, StaticExpr};
use crate::{Machine, Op, Stmt, StmtSyntax, Value};

#[k::claim(all_paths, label = "total-equation")]
fn total_equation(
    k::cells! {
        k: k::configuration::KCell(M3dTotal(4), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(5, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "partial-equation")]
fn partial_equation(
    k::cells! {
        k: k::configuration::KCell(M3dPositive(7), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "explicit-priority")]
fn explicit_priority(
    k::cells! {
        k: k::configuration::KCell(M3dPriority(0), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(111, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "static-alias")]
fn static_alias(
    k::cells! {
        k: k::configuration::KCell(StaticExpr::M3dZero(), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(0, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "context-alias")]
fn context_alias(
    k::cells! {
        k: k::configuration::KCell(StaticExpr::M3dTwice(Op::Add(1, 2)), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(6, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "addition-1")]
fn addition_one(
    k::cells! {
        k: k::configuration::KCell(Op::Add(3, 4), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "addition-2")]
fn addition_two(
    k::cells! {
        k: k::configuration::KCell(Op::Add(k::id!("$s"), k::id!("$n")), tail @ ..),
        env: k::configuration::Cell(map![
            k::id!("$s") -> 3,
            k::id!("$n") -> 4,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") -> 3,
            k::id!("$n") -> 4,
        ]),
        ..state
    }
}

#[k::claim(all_paths, label = "addition-var")]
#[k::requires(int::eq(n, 4))]
fn addition_var(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Op::Add(3, n), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "pre-branch-proved")]
fn pre_branch_proved(
    branch: Term<Bool>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$n"), 7),
                StmtSyntax::IfThenElse(
                    branch,
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
                ),
            )
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::IfThenElse(
            branch,
            StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
            StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
        )),
        env: k::configuration::Cell(map![k::id!("$n") -> 7]),
        ..state
    }
}

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

#[k::claim(all_paths, label = "branching-program")]
#[k::exists(environment: Map)]
fn branching_program(
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$n"), 7),
                StmtSyntax::IfThenElse(
                    k::anonymous!(Bool, "_B_PROGRAM"),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(k::anonymous!(Map, "_ENV")),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(environment),
        ..state
    }
}

#[k::claim(all_paths, label = "branching-deadcode")]
#[k::exists(n: Int)]
#[k::ensures(k::or_bool![int::eq(n, 5), int::eq(n, 6)])]
fn branching_deadcode(
    branch: Term<Bool>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$n"), 7),
                StmtSyntax::IfThenElse(
                    branch,
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
                    StmtSyntax::Block(StmtSyntax::IfThenElse(
                        Op::Not(branch),
                        StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
                        StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 4)),
                    )),
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

#[k::claim(all_paths, label = "while-cut-rule")]
fn while_cut_rule(
    condition: Term<Bool>,
    body: Stmt,
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::While(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::IfThenElse(
                condition,
                StmtSyntax::Block(StmtSyntax::Sequence(body, StmtSyntax::While(condition, body))),
                StmtSyntax::EmptyBlock(),
            ),
            ..tail
        ),
        ..state
    }
}

#[k::claim(all_paths, label = "while-cut-rule-delayed")]
#[k::exists(new_value: Value)]
fn while_cut_rule_delayed(
    condition: Term<Bool>,
    body: Stmt,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(StmtSyntax::Assign(k::id!("$n"), 7), StmtSyntax::While(condition, body)),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") -> k::anonymous!(Value, "_OLD_VALUE")
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::IfThenElse(
                condition,
                StmtSyntax::Block(StmtSyntax::Sequence(body, StmtSyntax::While(condition, body))),
                StmtSyntax::EmptyBlock(),
            ),
            ..tail
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> new_value]),
        ..state
    }
}

#[k::claim(all_paths, label = "sum-loop")]
#[k::requires(int::le(0, n))]
fn sum_loop(
    s: Term<Int>,
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::While(
                Op::Lt(0, k::id!("$n")),
                StmtSyntax::Block(StmtSyntax::Sequence(
                    StmtSyntax::Assign(k::id!("$s"), Op::Add(k::id!("$s"), k::id!("$n"))),
                    StmtSyntax::Assign(k::id!("$n"), Op::Sub(k::id!("$n"), 1)),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$s") -> s,
            k::id!("$n") -> n,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") -> int::add(s, int::div(int::mul(n, int::add(n, 1)), 2)),
            k::id!("$n") -> 0,
        ]),
        ..state
    }
}

#[k::claim(all_paths, label = "sum-N")]
#[k::requires(int::le(0, n))]
fn sum_n(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$s"), 0),
                StmtSyntax::Sequence(
                    StmtSyntax::Assign(k::id!("$n"), n),
                    StmtSyntax::While(
                        Op::Lt(0, k::id!("$n")),
                        StmtSyntax::Block(StmtSyntax::Sequence(
                            StmtSyntax::Assign(k::id!("$s"), Op::Add(k::id!("$s"), k::id!("$n"))),
                            StmtSyntax::Assign(k::id!("$n"), Op::Sub(k::id!("$n"), 1)),
                        )),
                    ),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![.Map]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") -> int::div(int::mul(n, int::add(n, 1)), 2),
            k::id!("$n") -> 0,
        ]),
        ..state
    }
}

#[k::claim(all_paths, label = "bmc-loop-concrete")]
#[k::exists(n: Int)]
#[k::ensures(int::lt(0, n))]
fn bmc_loop_concrete(
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::While(
                Op::Le(0, k::id!("$n")),
                StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), Op::Add(k::id!("$n"), Op::Neg(1)))),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> 1]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") -> n]),
        ..state
    }
}

#[k::claim(all_paths, label = "bmc-loop-symbolic")]
#[k::exists(n: Int)]
#[k::requires(int::le(0, s))]
#[k::ensures(int::lt(0, n))]
fn bmc_loop_symbolic(
    s: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::While(
                Op::Le(k::id!("$s"), k::id!("$n")),
                StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), Op::Add(k::id!("$n"), Op::Neg(1)))),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") -> 1,
            k::id!("$s") -> s,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") -> n,
            k::id!("$s") -> s,
        ]),
        ..state
    }
}

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

#[k::claim(all_paths, label = "two-sum-spec", circularity)]
#[k::requires(bool::and(int::ge(n, 0), int::ge(m, 0)))]
fn two_sum_spec(
    n: Term<Int>,
    m: Term<Int>,
    s1: Term<Int>,
    s2: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::While(
                    Op::Not(Op::Le(k::id!("$n"), 0)),
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        StmtSyntax::Assign(k::id!("$s1"), Op::Add(k::id!("$s1"), k::id!("$n"))),
                        StmtSyntax::Assign(k::id!("$n"), Op::Add(k::id!("$n"), Op::Neg(1))),
                    )),
                ),
                StmtSyntax::While(
                    Op::Not(Op::Le(k::id!("$m"), 0)),
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        StmtSyntax::Assign(k::id!("$s2"), Op::Add(k::id!("$s2"), k::id!("$m"))),
                        StmtSyntax::Assign(k::id!("$m"), Op::Add(k::id!("$m"), Op::Neg(1))),
                    )),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") -> n,
            k::id!("$m") -> m,
            k::id!("$s1") -> s1,
            k::id!("$s2") -> s2,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") -> 0,
            k::id!("$m") -> 0,
            k::id!("$s1") -> int::add(
                s1,
                int::div(int::mul(int::add(n, 1), n), 2),
            ),
            k::id!("$s2") -> int::add(
                s2,
                int::div(int::mul(int::add(m, 1), m), 2),
            ),
        ]),
        ..state
    }
}
