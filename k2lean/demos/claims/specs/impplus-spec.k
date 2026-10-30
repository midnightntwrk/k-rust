// K claims over IMP++ (K's tutorial, pl-tutorial/1_k/4_imp++/lesson_7/imp.k), example material of
// `k2lean claims` on a definition whose `Step` is not a function (design.md §3.8): its rules match
// two threads of the thread cell map (`join`), so its `Step` is ranked, and strict operators heat
// either argument first. `kc_auto` steps by every successor (`KClaims.ExecSucc`), and, where the
// successors do not reduce (a symbolic rest of `<k>`, a symbolic thread id or store location, a
// frame of `<env>` or `<store>`), by the cases of `Step`, whose map premises are located in the
// claim's description of each map (`KClaims.MapLoc`); a target's map is matched by its bindings,
// key by key (`kc_map_ext`).
// Each configuration has exactly one thread: with other threads abstracted, all-path reachability
// would quantify over their runs too, and one that runs forever never lets this one finish. The
// stream cells are empty or concrete: with a variable there, K's stdin/stdout rules (priorities 25,
// 30) could apply first.
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
  // CLM-9: a symbolic rest of `<k>`; the cooling rules' matchers read it
  claim [add-frame]:
    <threads> <thread>... <id> 0 </id> <k> 1 + 2; => .K ...</k> ...</thread> </threads>
    <input> .List </input> <output> .List </output>

  // CLM-10: the thread's id symbolic, a key of the thread map
  claim [add-id]:
    <threads> <thread>... <k> 1 + 2; => .K </k> ...</thread> </threads>
    <input> .List </input> <output> .List </output>

  // CLM-10: a store location symbolic, each map exactly one binding
  claim [var-one]:
    <threads> <thread> <id> 0 </id> <k> n + 1; => .K </k> <env> n |-> L:Int </env> </thread> </threads>
    <store> L |-> 5 </store>
    <input> .List </input> <output> .List </output>

  // CLM-10: the same with the rest of each map symbolic
  claim [var-rest]:
    <threads> <thread> <id> 0 </id> <k> n + 1; => .K </k> <env> n |-> L:Int ... </env> </thread> </threads>
    <store>... L |-> 5 ...</store>
    <input> .List </input> <output> .List </output>

  // the cells of the tutorial's own tests/proofs/sum-spec.k (abstract id, two variables at
  // symbolic locations, frames, its stream cells), with one lookup
  claim [look]:
    <threads><thread>...
      <k> n; => .K ...</k>
      <env>... n |-> LN:Int sum |-> LSUM:Int ...</env>
    ...</thread></threads>
    <input> ListItem(#buffer("\n" ~> .)) ListItem("off") ListItem(#istream(0)) </input>
    <output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer("" ~> .)) </output>
    <store>... LN |-> N:Int LSUM |-> S:Int ...</store>
    <generatedCounter> _ </generatedCounter>

  // a declaration: a fresh location in an empty store
  claim [decl]:
    <threads><thread>... <k> int n; => .K ...</k> <env> .Map => n |-> ?L:Int </env> ...</thread></threads>
    <input> .List </input> <output> .List </output>
    <store> .Map => ?L |-> 0 </store>
    <generatedCounter> C:Int => C +Int 1 </generatedCounter>

  // an assignment to a framed store at a symbolic location
  claim [assign-rest]:
    <threads><thread> <id> 0 </id> <k> n = 7; => .K </k> <env> n |-> L:Int ... </env></thread></threads>
    <store>... L |-> (_ => 7) ...</store>
    <input> .List </input> <output> .List </output>

  // an assignment under the cells of sum-spec.k: the target states the written store by its two
  // bindings over the frame, equal to the store the step built up to its bindings
  claim [assign-sum]:
    <threads><thread>...
      <k> sum = 7; => .K ...</k>
      <env>... n |-> LN:Int sum |-> LSUM:Int ...</env>
    ...</thread></threads>
    <input> ListItem(#buffer("\n" ~> .)) ListItem("off") ListItem(#istream(0)) </input>
    <output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer("" ~> .)) </output>
    <store>... LN |-> N:Int LSUM |-> (_:Int => 7) ...</store>
    <generatedCounter> _ </generatedCounter>

  // two declarations: two fresh locations, distinct by arithmetic (freshInt(C), freshInt(C + 1))
  claim [decl-two]:
    <threads><thread>... <k> int n, sum; => .K ...</k> <env> .Map => n |-> ?L:Int sum |-> ?M:Int </env> ...</thread></threads>
    <input> .List </input> <output> .List </output>
    <store> .Map => ?L |-> 0 ?M |-> 0 </store>
    <generatedCounter> C:Int => C +Int 2 </generatedCounter>
endmodule
