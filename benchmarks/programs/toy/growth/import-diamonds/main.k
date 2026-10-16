module MAIN
  imports INT
  syntax Int ::= f(Int) [function]
  rule f(X) => X +Int 1
  configuration <k> $PGM:Int </k>
endmodule
