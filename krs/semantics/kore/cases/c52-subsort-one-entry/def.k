// One stated subsort, Int < Val, and a sort Other with none: an Int in <k> matches a variable of
// sort Val through that subsort, and does not match a variable of sort Other.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax Val ::= Int
  syntax Other ::= o(Int)
  syntax S ::= done(Val) | other(Other)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:Val </k>
  rule <k> V:Val => done(V) </k>
  rule <k> X:Other => other(X) </k>
endmodule
