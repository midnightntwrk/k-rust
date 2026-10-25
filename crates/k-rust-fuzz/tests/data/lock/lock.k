// The list-shaped stall benchmark (FZ-14): a combination lock that reads its keys from one
// `List` hole, `$KEYS`, after the corpus proposer's motivating case (ARCHITECTURE 8.5: a
// sequence-shaped data hole, such as a `List` of transactions). The program is `open`; the
// keys are the configuration variable `$KEYS:List`, a list of `Int`s.
//
// - The lock turns through the phases `p0` .. `p5`: in phase k it consumes the next key, and
//   cell `l(k+1)` moves it to phase k+1 when that key passes the cell's guard. Cell k fires
//   only on a list whose first k-1 keys fired cells 1 .. k-1, in that order.
// - Every rule of the lock has `turn` at the head of `<k>` on both sides, and the phase is a
//   cell, as a ledger keeps its state in cells and loops over its transactions: the rule graph
//   puts every cell one edge before every other, so it says nothing about how far a list got.
// - `lu` is unreachable (a negative control): its nonlinear guard has no integer solution.
//
// The guards of one phase are pairwise disjoint, and the `owise` rule `jam` ends the walk when
// the list is empty or no cell's guard holds, so every list has exactly one path and ends
// naturally with an empty `<k>`. `research/stall-benchmark.md` in the fz26 notes gives the
// guards and the proposers meant to open them.

module LOCK-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "open"  [symbol(open)]
endmodule

module LOCK
  imports LOCK-SYNTAX
  imports INT
  imports BOOL
  imports LIST

  syntax KItem ::= "turn"  [symbol(turn)]
  syntax Phase ::= "p0" [symbol(p0)] | "p1" [symbol(p1)] | "p2" [symbol(p2)]
                 | "p3" [symbol(p3)] | "p4" [symbol(p4)] | "p5" [symbol(p5)]

  configuration <k> $PGM:Pgm </k>
                <keys> $KEYS:List </keys>
                <phase> p0 </phase>

  rule [begin]: <k> open => turn ... </k>

  rule [l1]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p0 => p1 </phase>
    requires X ==Int 17
  rule [l2]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p1 => p2 </phase>
    requires X >Int 1000 andBool X <Int 1100
  rule [l3]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p2 => p3 </phase>
    requires X ==Int 31337
  rule [lu]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p2 => p5 </phase>
    requires X *Int X ==Int 2
  rule [l4]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p3 => p4 </phase>
    requires X <Int -5000 andBool X >Int -5100
  rule [l5]: <k> turn ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
             <phase> p4 => p5 </phase>
    requires X ==Int 4242

  rule [jam]: <k> turn => .K ... </k> [owise]
endmodule
