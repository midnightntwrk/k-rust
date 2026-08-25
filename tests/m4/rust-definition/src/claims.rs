//! Complete M4 proof corpus: all 15 upstream IMP claims plus five adjuncts.

use k::Term;
use k::builtin::{Bool, Int, Map, bool, int};
#[allow(unused_imports)]
use k::map;

use crate::static_adjunct::{M3dPositive, M3dPriority, M3dTotal, M3dTwice, M3dZero};
use crate::{
    Add, Assign, Block, EmptyBlock, IfThenElse, Le, Lt, Machine, Neg, Not, Sequence, Stmt,
    Sub, Value, While,
};

type ValueSort = dyn Value;

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
        k: k::configuration::KCell(M3dZero(), tail @ ..),
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
        k: k::configuration::KCell(M3dTwice(Add(1, 2)), tail @ ..),
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
        k: k::configuration::KCell(Add(3, 4), tail @ ..),
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
        k: k::configuration::KCell(Add(k::id!("$s"), k::id!("$n")), tail @ ..),
        env: k::configuration::Cell(map![
            k::id!("$s") => 3,
            k::id!("$n") => 4,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(7, ..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") => 3,
            k::id!("$n") => 4,
        ]),
        ..state
    }
}

#[k::claim(all_paths, label = "addition-var")]
#[k::requires(int::eq(n, 4))]
fn addition_var(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Add(3, n), tail @ ..),
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
            Sequence(
                Assign(k::id!("$n"), 7),
                IfThenElse(
                    branch,
                    Block(Assign(k::id!("$n"), 6)),
                    Block(Assign(k::id!("$n"), 5)),
                ),
            )
        ),
        env: k::configuration::Cell(map![k::id!("$n") => 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(IfThenElse(
            branch,
            Block(Assign(k::id!("$n"), 6)),
            Block(Assign(k::id!("$n"), 5)),
        )),
        env: k::configuration::Cell(map![k::id!("$n") => 7]),
        ..state
    }
}

#[k::claim(all_paths, label = "branching")]
#[k::exists(n: Int)]
#[k::ensures(k::or_bool![int::eq(n, 5), int::eq(n, 6)])]
fn branching(
    k::cells! {
        k: k::configuration::KCell(
            Sequence(
                Assign(k::id!("$n"), 7),
                IfThenElse(
                    k::anonymous!(Bool, "_B"),
                    Block(Assign(k::id!("$n"), 6)),
                    Block(Assign(k::id!("$n"), 5)),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") => 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") => n]),
        ..state
    }
}

#[k::claim(all_paths, label = "branching-program")]
#[k::exists(environment: Map)]
fn branching_program(
    k::cells! {
        k: k::configuration::KCell(
            Sequence(
                Assign(k::id!("$n"), 7),
                IfThenElse(
                    k::anonymous!(Bool, "_B_PROGRAM"),
                    Block(Assign(k::id!("$n"), 6)),
                    Block(Assign(k::id!("$n"), 5)),
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
            Sequence(
                Assign(k::id!("$n"), 7),
                IfThenElse(
                    branch,
                    Block(Assign(k::id!("$n"), 6)),
                    Block(IfThenElse(
                        Not(branch),
                        Block(Assign(k::id!("$n"), 5)),
                        Block(Assign(k::id!("$n"), 4)),
                    )),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") => 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") => n]),
        ..state
    }
}

#[k::claim(all_paths, label = "while-cut-rule")]
fn while_cut_rule(
    condition: Term<Bool>,
    body: Term<dyn Stmt>,
    k::cells! {
        k: k::configuration::KCell(While(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(
            IfThenElse(
                condition,
                Block(Sequence(body, While(condition, body))),
                EmptyBlock(),
            ),
            ..tail
        ),
        ..state
    }
}

#[k::claim(all_paths, label = "while-cut-rule-delayed")]
#[k::exists(new_value: ValueSort)]
fn while_cut_rule_delayed(
    condition: Term<Bool>,
    body: Term<dyn Stmt>,
    k::cells! {
        k: k::configuration::KCell(
            Sequence(Assign(k::id!("$n"), 7), While(condition, body)),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") => k::anonymous!(ValueSort, "_OLD_VALUE")
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(
            IfThenElse(
                condition,
                Block(Sequence(body, While(condition, body))),
                EmptyBlock(),
            ),
            ..tail
        ),
        env: k::configuration::Cell(map![k::id!("$n") => new_value]),
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
            While(
                Lt(0, k::id!("$n")),
                Block(Sequence(
                    Assign(k::id!("$s"), Add(k::id!("$s"), k::id!("$n"))),
                    Assign(k::id!("$n"), Sub(k::id!("$n"), 1)),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$s") => s,
            k::id!("$n") => n,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") => int::add(s, int::div(int::mul(n, int::add(n, 1)), 2)),
            k::id!("$n") => 0,
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
            Sequence(
                Assign(k::id!("$s"), 0),
                Sequence(
                    Assign(k::id!("$n"), n),
                    While(
                        Lt(0, k::id!("$n")),
                        Block(Sequence(
                            Assign(k::id!("$s"), Add(k::id!("$s"), k::id!("$n"))),
                            Assign(k::id!("$n"), Sub(k::id!("$n"), 1)),
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
            k::id!("$s") => int::div(int::mul(n, int::add(n, 1)), 2),
            k::id!("$n") => 0,
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
            While(
                Le(0, k::id!("$n")),
                Block(Assign(k::id!("$n"), Add(k::id!("$n"), Neg(1)))),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") => 1]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") => n]),
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
            While(
                Le(k::id!("$s"), k::id!("$n")),
                Block(Assign(k::id!("$n"), Add(k::id!("$n"), Neg(1)))),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") => 1,
            k::id!("$s") => s,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") => n,
            k::id!("$s") => s,
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
            While(
                Not(Le(k::id!("$n"), 0)),
                Block(Sequence(
                    Assign(k::id!("$s"), Add(k::id!("$s"), k::id!("$n"))),
                    Assign(k::id!("$n"), Add(k::id!("$n"), Neg(1))),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") => n,
            k::id!("$s") => s,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") => 0,
            k::id!("$s") => int::add(
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
            Sequence(
                While(
                    Not(Le(k::id!("$n"), 0)),
                    Block(Sequence(
                        Assign(k::id!("$s1"), Add(k::id!("$s1"), k::id!("$n"))),
                        Assign(k::id!("$n"), Add(k::id!("$n"), Neg(1))),
                    )),
                ),
                While(
                    Not(Le(k::id!("$m"), 0)),
                    Block(Sequence(
                        Assign(k::id!("$s2"), Add(k::id!("$s2"), k::id!("$m"))),
                        Assign(k::id!("$m"), Add(k::id!("$m"), Neg(1))),
                    )),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") => n,
            k::id!("$m") => m,
            k::id!("$s1") => s1,
            k::id!("$s2") => s2,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") => 0,
            k::id!("$m") => 0,
            k::id!("$s1") => int::add(
                s1,
                int::div(int::mul(int::add(n, 1), n), 2),
            ),
            k::id!("$s2") => int::add(
                s2,
                int::div(int::mul(int::add(m, 1), m), 2),
            ),
        ]),
        ..state
    }
}
