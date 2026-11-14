// Rewrite rules of several priorities: a rule whose requires fails does not block a larger
// priority; one that applies does; an [owise] rule applies only where nothing else does.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int) | d(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> a(X) => b(X) </k> requires X >Int 100 [priority(10)]
  rule <k> a(X) => c(X) </k> requires X >Int 0 [priority(20)]
  rule <k> a(X) => d(X) </k> [priority(30)]
  rule <k> c(X) => d(X +Int 1) </k>
  rule <k> c(X) => a(0 -Int X) </k> [owise]
endmodule
