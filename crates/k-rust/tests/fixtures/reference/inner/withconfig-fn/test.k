module TEST
  imports INT
  configuration <k> $PGM:K </k> <bar> 6 </bar>
  syntax Int ::= foo(Int) [function]
  rule [[ foo(0) => I ]] <bar> I </bar>
endmodule
