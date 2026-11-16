module C3-RULE-PRIO-OWISE
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> [priority(40)]
  rule <k> a(_) => c() </k> [owise]
endmodule
