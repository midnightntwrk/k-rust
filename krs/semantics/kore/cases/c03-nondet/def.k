// Rules of one priority give several successors; paths meet again (diamonds) and end in several
// distinct final configurations.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= p(Int, Int) | fin(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule <k> p(X, Y) => p(X -Int 1, Y) </k> requires X >Int 0
  rule <k> p(X, Y) => p(X, Y -Int 1) </k> requires Y >Int 0
  rule <k> p(0, 0) => fin(0) </k>
  rule <k> p(X, Y) => fin(X *Int 10 +Int Y) </k> requires X ==Int 0 orBool Y ==Int 0
endmodule
