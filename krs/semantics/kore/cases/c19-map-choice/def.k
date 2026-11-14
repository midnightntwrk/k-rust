// A rule whose left side is K |-> V M, with M a frame variable, matches every entry of the map:
// one successor per entry, each with the rest of the map bound to M.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= s(Map) | out(Int, Int, Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> s(K:Int |-> V:Int M:Map) => out(K, V, M) </k>
endmodule
