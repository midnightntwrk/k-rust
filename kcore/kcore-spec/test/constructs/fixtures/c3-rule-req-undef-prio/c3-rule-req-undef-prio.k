module C3-RULE-REQ-UNDEF-PRIO
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> requires 10 /Int X >Int 0 [priority(40)]
  rule <k> a(_) => c() </k>
endmodule
