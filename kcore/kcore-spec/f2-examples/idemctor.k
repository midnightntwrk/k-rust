module E2-IDEM-CTOR
  syntax Exp ::= "x" [symbol(x)] | "y" [symbol(y)] | Exp "|" Exp [idem, symbol(or)]
endmodule
