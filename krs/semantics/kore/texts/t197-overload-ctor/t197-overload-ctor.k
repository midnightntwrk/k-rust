// Two overloaded constructor productions: sum(Exp, Int) and sum(Exp, Exp).
module T197-OVERLOAD-CTOR
  imports INT
  syntax Exp ::= Int
               | sum(Exp, Int)             [symbol(sumEI), overload(sum)]
               | sum(Exp, Exp)             [symbol(sumEE), overload(sum)]
  configuration <k> $PGM:Exp </k>
  rule <k> sum(E:Exp, I:Int) => sum(E, E) ... </k>
endmodule
