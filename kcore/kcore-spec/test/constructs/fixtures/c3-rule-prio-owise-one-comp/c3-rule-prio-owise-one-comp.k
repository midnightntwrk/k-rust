module C3-RULE-PRIO-OWISE-ONE-COMP
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> [owise, priority(40)]
  rule <k> a(_) => c() </k>
endmodule
