// Set concatenation of sets with a common element: S SetItem(1) where S has the element 1. K's
// sources call the concatenation idempotent in one place and undefined on a common element in
// another; kore.k reads it as undefined. S SetItem(2) is the union of disjoint sets, and
// S |Set SetItem(1), the union operation, is total.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports SET
  syntax S ::= go(Set) | r(Int, Set)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports SET
  configuration <k> $PGM:S </k>
  rule <k> go(S) => r(1, S SetItem(1)) </k>
  rule <k> go(S) => r(2, S SetItem(2)) </k>
  rule <k> go(S) => r(3, S |Set SetItem(1)) </k>
endmodule
