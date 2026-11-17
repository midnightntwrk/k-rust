module T07-UNDEFINED-INITIAL-TERM
  imports INT
  syntax Cmd ::= a(Int) | b(Int)
  syntax Int ::= inv(Int) [function]
  configuration <k> $PGM:Cmd </k>
  rule inv(X) => 1 /Int X
  rule <k> a(X) => b(X) </k>
endmodule
