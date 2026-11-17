module C3-RULE-RHS-UNDEF-PRIO
  imports INT
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(10 /Int X) </k> [priority(40)]
  rule <k> a(_) => c() </k>
endmodule
