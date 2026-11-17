module T03-APPLIED-RULE-BLOCKS
  imports INT
  syntax Cmd ::= a(Int) | b(Int) | c(Int)
  configuration <k> $PGM:Cmd </k>
  rule <k> a(X) => b(10 /Int X) </k> [priority(40)]
  rule <k> a(X) => c(X) </k>
endmodule
