// K claims over IMP++ (K's tutorial, pl-tutorial/1_k/4_imp++/lesson_7/imp.k), example material of
// `k2lean claims` on a definition whose `Step` is not a function (design.md §3.8): its rules match
// two threads of the thread cell map (`join`), so its `Step` is ranked, and strict operators heat
// either argument first. `kc_auto` steps by every successor (`KClaims.ExecSucc`).
// Each configuration has exactly one thread: with other threads abstracted, all-path reachability
// would quantify over their runs too, and one that runs forever never lets this one finish. The
// stream cells are empty: with a variable there, K's stdin/stdout rules (priorities 25, 30) could
// apply first. The thread's id is a literal: a symbolic key of the thread map blocks the
// matchers' reduction in Lean (design.md §3.8).
requires "imp.k"

module IMPPLUS-SPEC
  imports IMP

  // an expression statement: heating, the addition, cooling, and the integer discarded
  claim [add]:
    <threads> <thread>... <id> 0 </id> <k> 1 + 2; => .K </k> ...</thread> </threads>
    <input> .List </input> <output> .List </output>

  // both arguments of `+` heat first in some run: every interleaving ends in `.K`
  claim [add-both]:
    <threads> <thread>... <id> 0 </id> <k> (1 + 2) + (3 + 4); => .K </k> ...</thread> </threads>
    <input> .List </input> <output> .List </output>

  // a block with no declarations: its environment is saved and restored
  claim [block]:
    <threads> <thread>... <id> 0 </id> <k> { 1 + 2; } => .K </k> ...</thread> </threads>
    <input> .List </input> <output> .List </output>
endmodule
