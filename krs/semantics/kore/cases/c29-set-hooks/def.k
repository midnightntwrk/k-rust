// The Set hooks on a two-element set: membership of a present and of a missing element, size,
// and the union with an element below, between and above the present ones, and with a present one.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports SET
  syntax S ::= go(Set) | r(Bool, Bool, Int, Set, Set, Set, Set)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports SET
  configuration <k> $PGM:S </k>
  rule <k> go(S) => r(1 in S, 5 in S, size(S), S |Set SetItem(0), SetItem(2) |Set S,
                      S |Set SetItem(9), S |Set SetItem(3)) </k>
endmodule
