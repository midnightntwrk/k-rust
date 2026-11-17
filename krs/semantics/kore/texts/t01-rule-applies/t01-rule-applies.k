module T01-RULE-APPLIES
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) | b(Int) | c(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> requires 10 /Int X >Int 0 [priority(40)]
  rule <k> a(X) => c(X) </k>
endmodule
