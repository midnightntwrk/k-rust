// Re-pin R0c-fix-4 (R0c-fix-3 review critical 1, the reviewer's lamf.k): lamrule.k with the lambda
// inside the equation of f, so the source head set is {f} and the lambda is a generated symbol.
module LAMFUN-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax Prog ::= start() [symbol(start)] | go(Map) [symbol(go)] | val(Int) [symbol(val)]
  syntax Int ::= f(Map) [function, symbol(f)]
endmodule
module LAMFUN
  imports LAMFUN-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start() => go((1 |-> 10) (2 |-> 20)) </k>
  rule [f]: f(M) => #fun((_K:Int |-> V:Int) _R:Map => V *Int 0)(M)
  rule [go]: <k> go(M) => val(f(M)) </k>
endmodule
