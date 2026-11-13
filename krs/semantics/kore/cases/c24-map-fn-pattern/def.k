// Function equations whose argument pattern is K |-> V M: total sums the values, whichever entry
// each step takes; keyOfBig takes the entry whose value satisfies its requires, which is not the
// first entry of the map, and its [owise] equation applies to no map that has such an entry.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map) | r(Int, Int)
  syntax Int ::= total(Map) [function]
               | keyOfBig(Map) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <k> $PGM:S </k>
  rule total(.Map) => 0
  rule total(_:Int |-> V:Int M:Map) => V +Int total(M)
  rule keyOfBig(K:Int |-> V:Int _:Map) => K requires V >Int 15
  rule keyOfBig(_) => 0 [owise]
  rule <k> go(M) => r(total(M), keyOfBig(M)) </k>
endmodule
