module M [not-lr1]
  imports INT
  imports M2
  syntax Stmt [locations]
  syntax Stmt ::= "skip"          [symbol(skip)]
  syntax Exp ::= Int
               | "(" Exp ")"      [bracket]
               | Exp "+" Exp      [symbol(plus), left, avoid, latex({#1}+{#2}), group(addg), format(%1 + %3)]
               | Exp "-" Exp      [symbol(minus), right, prefer, unparseAvoid, color(blue)]
               | Exp "==" Exp     [symbol(eq), non-assoc, unused]
               | Exp "*" Exp      [symbol(mul), applyPriority(1)]
               | Exp "/" Exp      [symbol(div), internal]
  syntax Exp ::= Int2Exp(Int)     [function, symbol(Int2Exp), returnsUnit]
  rule Int2Exp(I) => I
  syntax Word ::= r"[a-z]+"       [token, prec(2)]
  syntax Exp ::= w(Word)          [symbol(w), public]
               | v(Word)          [symbol(v), private]
  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
endmodule
module M2
  syntax Bar ::= bar()            [symbol(bar)]
endmodule
