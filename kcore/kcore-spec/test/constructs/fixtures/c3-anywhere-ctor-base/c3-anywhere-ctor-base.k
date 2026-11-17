module C3-ANYWHERE-CTOR-BASE
  imports INT
  syntax Exp ::= Int
               | sum(Exp, Int)             [symbol(sumEI), prefer]
               | sum(Exp, Exp)             [symbol(sumEE)]
  configuration <k> $PGM:Exp </k>
  rule <k> sum(E:Exp, I:Int) => sum(E, E) ... </k>
endmodule
