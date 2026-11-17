module T04-RULE-PRIORITY-OWISE
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) | b(Int) | c(Int) | d(Int) | e(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> [owise]
  rule <k> a(X) => c(X) </k> requires X >Int 0
  rule <k> a(X) => d(X) </k> requires X >Int 5 [priority(40)]
  rule <k> a(X) => e(X) </k> [priority(250)]
endmodule
