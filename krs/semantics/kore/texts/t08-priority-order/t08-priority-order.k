module T08-PRIORITY-ORDER
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) | b(Int) | c(Int)
  syntax Bool ::= loop(Int) [function]
  configuration <k> $PGM:Cmd </k>
  rule loop(X) => loop(X +Int 1)
  rule <k> a(X) => b(X) </k> requires X >Int 0
  rule <k> a(X) => c(X) </k> requires loop(X) [priority(60)]
endmodule
