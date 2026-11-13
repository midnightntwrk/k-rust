// An initial term that is undefined (a division by zero in a function the term applies) is no
// configuration: there is no final one.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int)
  syntax Int ::= inv(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule inv(X) => 1 /Int X
  rule <k> a(X) => b(X) </k>
endmodule
