module T02-STEP-SUCCESSORS
  imports INT
  syntax Cmd ::= a(Int) | b(Int) | c(Int) | d(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k>
  rule <k> a(X) => c(X +Int 1) </k>
  rule <k> a(X) => d(X) </k> [priority(60)]
endmodule
