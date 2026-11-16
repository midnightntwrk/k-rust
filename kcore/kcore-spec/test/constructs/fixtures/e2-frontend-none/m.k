module M
  imports INT
  imports M2
  syntax Stmt ::= "skip"          [symbol(skip)]
  syntax Exp ::= Int
               | Exp "+" Exp      [symbol(plus)]
               | Exp "-" Exp      [symbol(minus)]
               | Exp "==" Exp     [symbol(eq)]
               | Exp "*" Exp      [symbol(mul)]
               | Exp "/" Exp      [symbol(div)]
  syntax Exp ::= Int2Exp(Int)     [function, symbol(Int2Exp)]
  rule Int2Exp(I) => I
  syntax Word ::= r"[a-z]+"       [token]
  syntax Exp ::= w(Word)          [symbol(w)]
               | v(Word)          [symbol(v)]
  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
endmodule
module M2
  syntax Bar ::= bar()            [symbol(bar)]
endmodule
