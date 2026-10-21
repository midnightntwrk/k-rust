// Re-pin R0c-fix-4 (R0c-fix-3 review, the reviewer's control mapf.k): the map pattern of lamrule.k
// as f's own equation, a self pair.
module MAPFUN-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax Prog ::= start() [symbol(start)] | go(Map) [symbol(go)] | val(Int) [symbol(val)]
  syntax Int ::= f(Map) [function, symbol(f)]
endmodule
module MAPFUN
  imports MAPFUN-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start() => go((1 |-> 10) (2 |-> 20)) </k>
  rule [f]: f((_K:Int |-> V:Int) _R:Map) => V *Int 0
  rule [go]: <k> go(M) => val(f(M)) </k>
endmodule
