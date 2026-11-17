module T05-RULE-ENSURES-RESULT
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) | b(Int) | c(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(I) => b(I) </k> ensures I >Int 0
  rule <k> a(I) => c(I) </k> [priority(60)]
endmodule
