// The Map hooks on a two-entry map: lookup, lookup with a default (present and missing key),
// update of a present key and of a new key between the two present ones, removal of a present
// and of a missing key, in_keys and size.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports MAP
  syntax S ::= go(Map)
             | r(KItem, KItem, KItem, Map, Map, Map, Map, Bool, Bool, Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(M) => r(M[1], M[1] orDefault 0, M[5] orDefault 0, M[1 <- 7], M[2 <- 9],
                      M[1 <- undef], M[5 <- undef], 1 in_keys(M), 5 in_keys(M), size(M)) </k>
endmodule
