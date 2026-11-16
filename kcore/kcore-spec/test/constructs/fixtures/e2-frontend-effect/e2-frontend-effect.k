module E2-FRONTEND-EFFECT
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | pair(Exp, Exp)            [symbol(pair), hybrid, strict]
               | neg(Exp)                  [symbol(neg), strict, result(Val)]
               | sum(Exp, Int)             [symbol(sumEI), overload(sum)]
               | sum(Exp, Exp)             [symbol(sumEE), overload(sum)]
  syntax Val ::= Int
  syntax KResult ::= Int | Val
  syntax Exp ::= Int2Exp(Int)              [function, symbol(Int2Exp), returnsUnit]
  syntax Stmt ::= "skip"                   [symbol(skip)]
  syntax Stmt [locations]
  syntax Exp ::= free()                    [symbol(free)]
  syntax Int ::= init0()                   [function, total, symbol(init0)]
  rule init0() => 0
  configuration <k> $PGM:Exp </k> <c> init0() </c>
  rule <k> free() => ?X:Int ... </k>
  rule <k> sum(E:Exp, I:Int) => sum(E, E) ... </k>
endmodule
