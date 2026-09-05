module TEST
  imports INT
  configuration <k> $PGM:K </k> <bar> 6 </bar>
  syntax Int ::= foo(Int) [function]
  rule foo(I) => I +Int 1 requires I >Int 0
endmodule
