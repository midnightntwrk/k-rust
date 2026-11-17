module T06-FINAL-CONFIGURATION
  imports INT
  imports BOOL
  syntax Cmd ::= a(Int) | b(Int) | c(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(X) </k>
  rule <k> a(X) => c(X) </k>
  rule <k> b(X) => c(X +Int 1) </k> requires X >Int 0
endmodule
