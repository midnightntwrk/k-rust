module E2-COMM-CTOR
  syntax Exp ::= "x" [symbol(x)] | Exp "&" Exp [symbol(and), comm] | Exp "|" Exp [symbol(or), assoc]
endmodule
