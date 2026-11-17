module C3-RULE-HEAT-REQ
  imports INT
  imports BOOL
  syntax KResult ::= Int
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> requires X >Int 0 [heat]
endmodule
