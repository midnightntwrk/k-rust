// A rewrite rule with both owise and priority(40), alone in the text.
module T213-RULE-OWISE-PRIO40
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c() [symbol(c)]
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k> [owise, priority(40)]
endmodule
