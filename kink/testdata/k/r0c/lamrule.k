// Re-pin R0c-fix-4 (R0c-fix-3 review critical 1, the reviewer's lam.k): a generated lambda whose map
// pattern matches one subject in several ways, in a rewrite rule. Baseline: every matching gives
// V *Int 0 = 0. Mutant int-literal 0 -> 1: the lambda has two values on one input (no model).
module LAMRULE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax Prog ::= start() [symbol(start)] | go(Map) [symbol(go)] | val(Int) [symbol(val)]
endmodule
module LAMRULE
  imports LAMRULE-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start() => go((1 |-> 10) (2 |-> 20)) </k>
  rule [go]: <k> go(M) => val(#fun((_K:Int |-> V:Int) _R:Map => V *Int 0)(M)) </k>
endmodule
