// Element patterns whose key is fixed: by a domain value (2 |-> V M), by a variable bound
// earlier in the left side (b(K, K |-> V M)); an element chosen under a requires on its value;
// and a pattern without a frame, which matches only a map of exactly its entries.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map) | a(Map) | b(Int, Map) | c(Map) | d(Map) | r(Int, Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(M) => a(M) </k>
  rule <k> go(M) => b(3, M) </k>
  rule <k> go(M) => c(M) </k>
  rule <k> go(M) => d(M) </k>
  rule <k> a(2 |-> V:Int M:Map) => r(V, M) </k>
  rule <k> b(K:Int, K |-> V:Int M:Map) => r(V, M) </k>
  rule <k> c(K:Int |-> V:Int _:Map) => r(K, .Map) </k> requires V >Int 15
  rule <k> d(K:Int |-> _:Int) => r(K, .Map) </k>
endmodule
