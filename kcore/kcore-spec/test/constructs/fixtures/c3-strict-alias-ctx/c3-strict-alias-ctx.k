module C3-STRICT-ALIAS-CTX
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | neg(Exp)        [symbol(neg), strict]
               | pair(Exp, Exp)  [symbol(pair), strict]
               | Exp "+" Exp     [symbol(plus), strict]
               | twice(Exp)      [symbol(twice), strict(c)]
  syntax Val ::= Int
  syntax KResult ::= Int | Val
  configuration <k> $PGM:Exp </k> <m> 0 </m>
  context alias [c]: <k> HERE:K ... </k> <m> 1 </m>
endmodule
