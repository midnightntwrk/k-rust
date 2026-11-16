module E1-SENTENCES
  imports INT
  syntax Exp ::= Int | Exp "+" Exp          [seqstrict, symbol(plus)]
               | neg(Exp)                   [symbol(neg)]
  syntax KResult ::= Int
  configuration <k> $PGM:Exp </k> <out> 0 </out>
  context neg(HOLE:Exp)
  context alias [c]: <k> HERE:K ... </k>
  syntax Exp ::= twice(Exp)                 [strict(c), symbol(twice)]
  rule I1:Int + I2:Int => I1 +Int I2
  rule neg(I:Int) => 0 -Int I
  rule twice(I:Int) => I *Int 2
endmodule
