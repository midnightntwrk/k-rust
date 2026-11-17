module T162-SEQSTRICT-ORDER
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | neg(Exp)        [symbol(neg), strict]
               | pair(Exp, Exp)  [symbol(pair), strict]
               | Exp "+" Exp     [symbol(plus), seqstrict]
               | twice(Exp)      [symbol(twice), strict]
  syntax Val ::= Int
  syntax KResult ::= Int | Val
  configuration <k> $PGM:Exp </k>
  context alias [c]: <k> HERE:K ... </k>
endmodule
