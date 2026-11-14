// A rule whose left side is SetItem(X) S, with S a frame variable, matches every element of the
// set: one successor per element, each with the rest of the set bound to S.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports SET
  syntax S ::= s(Set) | out(Int, Set)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports SET
  configuration <k> $PGM:S </k>
  rule <k> s(SetItem(X:Int) S:Set) => out(X, S SetItem(X +Int 10)) </k>
endmodule
