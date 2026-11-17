module C3-RULE-ENS-PRIO-COMP
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> ensures X >=Int 0 [priority(40)]
  rule <k> a(_) => c() </k>
endmodule
