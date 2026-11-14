// #if is a function of its three arguments: an undefined branch makes it undefined even where
// the condition does not select it, and so does an undefined operand of andBool.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:S </k>
  rule <k> a(X) => b(#if X ==Int 0 #then 1 #else 10 /Int X #fi) </k> [priority(40)]
  rule <k> a(X) => c(X) </k> requires X =/=Int 0 andBool 10 /Int X >Int 0
endmodule
